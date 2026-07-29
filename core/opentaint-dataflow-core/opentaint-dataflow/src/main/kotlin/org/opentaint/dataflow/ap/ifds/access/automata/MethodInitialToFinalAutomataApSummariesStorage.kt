package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.AnyFieldMarkExclusions
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
) : CommonF2FSummary<AutomataInitialAccess, AutomataFinalAccess>(methodInitialStatement),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createStorage(): Storage<AutomataInitialAccess, AutomataFinalAccess> =
        InitialToFinalApStorage()
}

private class InitialToFinalApStorage :
    CommonF2FSummary.Storage<AutomataInitialAccess, AutomataFinalAccess> {
    private val initialFactGraphIndex = object2IntMap<AccessGraph>()
    private val initialFactGraphs = arrayListOf<AccessGraph>()
    private val finalFactGraphStorages = arrayListOf<FinalApStorage>()

    private val initialGraphIndex = GraphIndex()

    override fun add(
        edges: List<CommonF2FSummary.StorageEdge<AutomataInitialAccess, AutomataFinalAccess>>,
        added: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
    ) {
        val modifiedStorages = BitSet()

        for (edge in edges) {
            val storageIdx = getOrCreateStorageIdx(edge.initial)
            val storage = finalFactGraphStorages[storageIdx]

            if (storage.add(edge.exclusion, edge.final)) {
                modifiedStorages.set(storageIdx)
            }
        }

        modifiedStorages.forEach { storageIdx ->
            val storage = finalFactGraphStorages[storageIdx]
            val storageEdges =
                mutableListOf<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>()
            storage.addAndResetDelta(storageEdges)

            val initialAg = initialFactGraphs[storageIdx]
            storageEdges.mapTo(added) { it.setInitialAp(initialAg) }
        }
    }

    private fun getOrCreateStorageIdx(initial: AutomataInitialAccess): Int {
        return initialFactGraphIndex.getOrCreateIndex(initial) { newIdx ->
            initialFactGraphs.add(initial)
            finalFactGraphStorages.add(FinalApStorage())
            initialGraphIndex.add(initial, newIdx)
            return newIdx
        }
    }

    override fun collectSummariesTo(
        dst: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
        initialFactPatter: AutomataFinalAccess?,
    ) {
        if (initialFactPatter != null) {
            filterEdgesTo(dst, initialFactPatter)
        } else {
            allEdgesTo(dst)
        }
    }

    private fun allEdgesTo(
        dst: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
    ) {
        finalFactGraphStorages.concurrentReadSafeForEach { idx, finalStorage ->
            val initialAg = initialFactGraphs[idx]
            collectToListWithPostProcess(dst, {
                finalStorage.allEdgesTo(it)
            }, {
                it.setInitialAp(initialAg)
            })
        }
    }

    private fun filterEdgesTo(
        dst: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
        accessPattern: AutomataFinalAccess,
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
    private var exclusionStorage: ExclusionSet? = null
    private var anyFieldMarkExclusions: AnyFieldMarkExclusions? = null
    private val agStorage = AccessGraphStorageWithCompression()
    private var stateModified: Boolean = false

    fun addAndResetDelta(
        modified: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
    ) {
        val exclusion = exclusionStorage ?: return
        val rootExclusions = anyFieldMarkExclusions ?: return
        if (stateModified) {
            agStorage.allGraphs().forEach { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setExclusion(exclusion)
                    .setExitAp(AutomataFinalAccess(ag, rootExclusions))
            }
        } else {
            agStorage.mapAndResetDelta { ag ->
                modified += FactToFactEdgeBuilderBuilder()
                    .setExclusion(exclusion)
                    .setExitAp(AutomataFinalAccess(ag, rootExclusions))
            }
        }

        stateModified = false
    }

    fun add(exclusion: ExclusionSet, finalAp: AutomataFinalAccess): Boolean {
        val mergedState = exclusionStorage?.union(exclusion) ?: exclusion
        val mergedAnyFieldMarkExclusions =
            anyFieldMarkExclusions?.join(finalAp.anyFieldMarkExclusions)
                ?: finalAp.anyFieldMarkExclusions
        if (mergedState === exclusionStorage &&
            mergedAnyFieldMarkExclusions === anyFieldMarkExclusions
        ) {
            return agStorage.add(finalAp.access)
        }

        exclusionStorage = mergedState
        anyFieldMarkExclusions = mergedAnyFieldMarkExclusions
        agStorage.add(finalAp.access)
        stateModified = true

        return true
    }

    fun allEdgesTo(
        dst: MutableList<F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>>,
    ) {
        val exclusion = exclusionStorage ?: return
        val rootExclusions = anyFieldMarkExclusions ?: return
        collectToListWithPostProcess(dst, {
            agStorage.allGraphsTo(it)
        }, { ag ->
            FactToFactEdgeBuilderBuilder()
                .setExclusion(exclusion)
                .setExitAp(AutomataFinalAccess(ag, rootExclusions))
        })
    }

    override fun toString(): String = "($exclusionStorage -> $agStorage)"
}

class FactToFactEdgeBuilderBuilder :
    F2FBBuilder<AutomataInitialAccess, AutomataFinalAccess>(),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun nonNullIAP(iap: AutomataInitialAccess?): AutomataInitialAccess = iap!!
}
