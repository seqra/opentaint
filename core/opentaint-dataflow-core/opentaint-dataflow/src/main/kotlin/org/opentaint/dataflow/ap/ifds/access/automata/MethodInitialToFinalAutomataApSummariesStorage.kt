package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.FactFlowState
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
) : CommonF2FSummary<AccessGraph, AccessGraph>(methodInitialStatement),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createStorage(): Storage<AccessGraph, AccessGraph> = InitialToFinalApStorage()
}

private class InitialToFinalApStorage : CommonF2FSummary.Storage<AccessGraph, AccessGraph> {
    private val initialFactGraphIndex = object2IntMap<AccessGraph>()
    private val initialFactGraphs = arrayListOf<AccessGraph>()
    private val finalFactGraphStorages = arrayListOf<FinalApStorage>()

    private val initialGraphIndex = GraphIndex()

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<AccessGraph, AccessGraph>>,
        added: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>,
    ) {
        val modifiedStorages = BitSet()

        for (edge in edges) {
            val storageIdx = getOrCreateStorageIdx(edge.initial)
            val storage = finalFactGraphStorages[storageIdx]

            if (storage.add(edge.flowState, edge.final)) {
                modifiedStorages.set(storageIdx)
            }
        }

        modifiedStorages.forEach { storageIdx ->
            val storage = finalFactGraphStorages[storageIdx]
            val storageEdges = mutableListOf<F2FBBuilder<AccessGraph, AccessGraph>>()
            storage.addAndResetDelta(storageEdges)

            val initialAg = initialFactGraphs[storageIdx]
            storageEdges.mapTo(added) { it.setInitialAp(initialAg) }
        }
    }

    private fun getOrCreateStorageIdx(initial: AccessGraph): Int {
        return initialFactGraphIndex.getOrCreateIndex(initial) { newIdx ->
            initialFactGraphs.add(initial)
            finalFactGraphStorages.add(FinalApStorage())
            initialGraphIndex.add(initial, newIdx)
            return newIdx
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>,
        initialFactPatter: AccessGraph?,
    ) {
        if (initialFactPatter != null) {
            filterEdgesTo(dst, initialFactPatter)
        } else {
            allEdgesTo(dst)
        }
    }

    private fun allEdgesTo(dst: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>) {
        finalFactGraphStorages.concurrentReadSafeForEach { idx, finalStorage ->
            val initialAg = initialFactGraphs[idx]
            collectToListWithPostProcess(dst, {
                finalStorage.allEdgesTo(it)
            }, {
                it.setInitialAp(initialAg)
            })
        }
    }

    private fun filterEdgesTo(dst: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>, accessPattern: AccessGraph) {
        initialGraphIndex.localizeGraphHasDeltaWithIndexedGraph(accessPattern).forEach { storageIdx ->
            val initialAg = initialFactGraphs[storageIdx]

            if (accessPattern.delta(initialAg).isEmpty()) {
                return@forEach
            }

            val finalStorage = finalFactGraphStorages[storageIdx]
            collectToListWithPostProcess(dst, {
                finalStorage.allEdgesTo(it)
            }, {
                it.setInitialAp(initialAg)
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
    private var flowStateStorage: FactFlowState? = null
    private val agStorage = AccessGraphStorageWithCompression()
    private var stateModified: Boolean = false

    fun addAndResetDelta(modified: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>) {
        val flowState = flowStateStorage ?: return
        if (stateModified) {
            agStorage.allGraphs().forEach { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setFlowState(flowState)
                    .setExitAp(ag)
            }
        } else {
            agStorage.mapAndResetDelta { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setFlowState(flowState)
                    .setExitAp(ag)
            }
        }

        stateModified = false
    }

    fun add(flowState: FactFlowState, finalApAg: AccessGraph): Boolean {
        val mergedState = flowStateStorage?.join(flowState) ?: flowState
        if (mergedState === flowStateStorage) {
            return agStorage.add(finalApAg)
        }

        flowStateStorage = mergedState
        agStorage.add(finalApAg)
        stateModified = true

        return true
    }

    fun allEdgesTo(dst: MutableList<F2FBBuilder<AccessGraph, AccessGraph>>) {
        val flowState = flowStateStorage ?: return
        collectToListWithPostProcess(dst, {
            agStorage.allGraphsTo(it)
        }, { ag ->
            FactToFactEdgeBuilderBuilder()
                .setFlowState(flowState)
                .setExitAp(ag)
        })
    }

    override fun toString(): String = "($flowStateStorage -> $agStorage)"
}

class FactToFactEdgeBuilderBuilder : F2FBBuilder<AccessGraph, AccessGraph>(),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun nonNullIAP(iap: AccessGraph?): AccessGraph = iap!!
}
