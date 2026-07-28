package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.util.forEach
import org.opentaint.dataflow.util.getOrCreateIndex
import org.opentaint.dataflow.util.object2IntMap
import java.util.BitSet
import java.util.concurrent.ConcurrentHashMap

class SideEffectRequirementAutomataApStorage : SideEffectRequirementApStorage {
    private val based = ConcurrentHashMap<AccessPathBase, Storage>()

    override fun add(requirements: List<InitialFactAp>): List<InitialFactAp> {
        val modifiedStorages = mutableListOf<Storage>()

        for (requirement in requirements) {
            requirement as AccessGraphInitialFactAp

            val storage = based.computeIfAbsent(requirement.base) { Storage(requirement.base) }
            storage.mergeAdd(requirement.access, requirement.flowState) ?: continue
            modifiedStorages.add(storage)
        }

        val result = mutableListOf<InitialFactAp>()
        modifiedStorages.forEach { it.getAndResetDelta(result) }
        return result
    }

    override fun filterTo(dst: MutableList<InitialFactAp>, fact: FinalFactAp) {
        val storage = based[fact.base] ?: return
        storage.find(dst, (fact as AccessGraphFinalFactAp).access)
    }

    override fun collectAllRequirementsTo(dst: MutableList<InitialFactAp>) {
        based.values.forEach { storage ->
            storage.find(dst, factAccess = null)
        }
    }

    private class Storage(
        private val base: AccessPathBase,
    ) {
        private val requirementGraphIndex = object2IntMap<AccessGraph>()
        private val requirementGraphs = arrayListOf<AccessGraph>()
        private val overrides = arrayListOf<BitSet>()
        private val removedRequirementGraphs = BitSet()
        private val requirementFlowStates = arrayListOf<FactFlowState>()

        private val graphIndex = GraphIndex()
        private val delta = BitSet()

        fun mergeAdd(requirementGraph: AccessGraph, requirementFlowState: FactFlowState): Unit? {
            val currentValueIndex = requirementGraphIndex.getOrCreateIndex(requirementGraph) { newIndex ->
                return addCompressed(requirementGraph, requirementFlowState, newIndex)
            }

            return updateFlowStateAtIdx(currentValueIndex, requirementFlowState)
        }

        private fun addCompressed(graph: AccessGraph, flowState: FactFlowState, idx: Int): Unit? {
            requirementGraphs.add(graph)
            requirementFlowStates.add(flowState)
            overrides.add(BitSet())

            val weakerGraphIdx = graphIndex.localizeGraphContainsAllIndexedGraph(graph)
            weakerGraphIdx.andNot(removedRequirementGraphs)
            if (!weakerGraphIdx.isEmpty) {
                val weakerIdx = weakerGraphIdx.nextSetBit(0)

                removedRequirementGraphs.set(idx)
                requirementGraphIndex.put(graph, weakerIdx)
                overrides[weakerIdx].set(idx)

                return updateFlowStateAtIdx(weakerIdx, flowState)
            }

            val strongerGraphIdx = graphIndex.localizeIndexedGraphContainsAllGraph(graph)
            strongerGraphIdx.andNot(removedRequirementGraphs)
            strongerGraphIdx.forEach { graphIdx ->
                removedRequirementGraphs.set(graphIdx)
                delta.clear(graphIdx)

                val removedGraph = requirementGraphs[graphIdx]
                val removedFlowState = requirementFlowStates[graphIdx]
                val removedGraphOverrides = overrides[graphIdx]

                requirementGraphIndex.put(removedGraph, idx)
                updateFlowStateAtIdx(idx, removedFlowState)

                removedGraphOverrides.forEach { overrideIdx ->
                    val overrideGraph = requirementGraphs[overrideIdx]
                    requirementGraphIndex.put(overrideGraph, idx)
                }

                val overrides = overrides[idx]
                overrides.set(graphIdx)
                overrides.or(removedGraphOverrides)
            }

            delta.set(idx)
            graphIndex.add(graph, idx)
            return Unit
        }

        private fun updateFlowStateAtIdx(idx: Int, flowState: FactFlowState): Unit? {
            val oldState = requirementFlowStates[idx]

            val newValue = oldState join flowState

            if (oldState === newValue) {
                return null
            }

            requirementFlowStates[idx] = newValue
            delta.set(idx)

            return Unit
        }

        fun getAndResetDelta(dst: MutableCollection<InitialFactAp>) {
            delta.forEach { idx ->
                val graph = requirementGraphs[idx]
                val flowState = requirementFlowStates[idx]
                dst.add(
                    AccessGraphInitialFactAp(
                        base, graph, flowState.exclusions, flowState.deepCleanEffects
                    )
                )
            }
            delta.clear()
        }

        fun find(
            collection: MutableList<InitialFactAp>,
            factAccess: AccessGraph?
        ) {
            if (factAccess == null) {
                val allIndices = BitSet(requirementGraphs.size).apply { set(0, requirementGraphs.size) }
                allIndices.andNot(removedRequirementGraphs)

                allIndices.forEach { i ->
                    val graph = requirementGraphs[i]
                    val flowState = requirementFlowStates[i]
                    collection += AccessGraphInitialFactAp(
                        base, graph, flowState.exclusions, flowState.deepCleanEffects
                    )
                }
                return
            }

            filter(factAccess, collection)
        }

        private fun filter(
            factAccess: AccessGraph,
            collection: MutableList<InitialFactAp>
        ) {
            val relevantGraphs = graphIndex.localizeGraphContainsAllIndexedGraph(factAccess)
            relevantGraphs.andNot(removedRequirementGraphs)
            relevantGraphs.forEach { graphIdx ->
                val graph = requirementGraphs[graphIdx]

                if (!factAccess.containsAll(graph)) {
                    return@forEach
                }

                val flowState = requirementFlowStates[graphIdx]
                collection += AccessGraphInitialFactAp(
                    base, graph, flowState.exclusions, flowState.deepCleanEffects
                )
            }
        }
    }
}
