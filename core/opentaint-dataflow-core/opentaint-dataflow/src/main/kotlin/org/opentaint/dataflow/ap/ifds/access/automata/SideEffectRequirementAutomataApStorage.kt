package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
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
            storage.mergeAdd(
                requirement.access,
                requirement.demandState,
                requirement.anyFieldCleanerEffects,
            ) ?: continue
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
        private val requirementDemandStates = arrayListOf<FactDemandState>()
        private val requirementCleanerEffects = arrayListOf<AnyFieldCleanerEffects>()

        private val graphIndex = GraphIndex()
        private val delta = BitSet()

        fun mergeAdd(
            requirementGraph: AccessGraph,
            requirementDemandState: FactDemandState,
            cleanerEffects: AnyFieldCleanerEffects,
        ): Unit? {
            val currentValueIndex = requirementGraphIndex.getOrCreateIndex(requirementGraph) { newIndex ->
                return addCompressed(
                    requirementGraph,
                    requirementDemandState,
                    cleanerEffects,
                    newIndex,
                )
            }

            return updateStateAtIdx(currentValueIndex, requirementDemandState, cleanerEffects)
        }

        private fun addCompressed(
            graph: AccessGraph,
            demandState: FactDemandState,
            cleanerEffects: AnyFieldCleanerEffects,
            idx: Int,
        ): Unit? {
            requirementGraphs.add(graph)
            requirementDemandStates.add(demandState)
            requirementCleanerEffects.add(cleanerEffects)
            overrides.add(BitSet())

            val weakerGraphIdx = graphIndex.localizeGraphContainsAllIndexedGraph(graph)
            weakerGraphIdx.andNot(removedRequirementGraphs)
            if (!weakerGraphIdx.isEmpty) {
                val weakerIdx = weakerGraphIdx.nextSetBit(0)

                removedRequirementGraphs.set(idx)
                requirementGraphIndex.put(graph, weakerIdx)
                overrides[weakerIdx].set(idx)

                return updateStateAtIdx(weakerIdx, demandState, cleanerEffects)
            }

            val strongerGraphIdx = graphIndex.localizeIndexedGraphContainsAllGraph(graph)
            strongerGraphIdx.andNot(removedRequirementGraphs)
            strongerGraphIdx.forEach { graphIdx ->
                removedRequirementGraphs.set(graphIdx)
                delta.clear(graphIdx)

                val removedGraph = requirementGraphs[graphIdx]
                val removedDemandState = requirementDemandStates[graphIdx]
                val removedCleanerEffects = requirementCleanerEffects[graphIdx]
                val removedGraphOverrides = overrides[graphIdx]

                requirementGraphIndex.put(removedGraph, idx)
                updateStateAtIdx(idx, removedDemandState, removedCleanerEffects)

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

        private fun updateStateAtIdx(
            idx: Int,
            demandState: FactDemandState,
            cleanerEffects: AnyFieldCleanerEffects,
        ): Unit? {
            val oldState = requirementDemandStates[idx]
            val oldEffects = requirementCleanerEffects[idx]
            val newState = oldState join demandState
            val newEffects = oldEffects join cleanerEffects

            if (oldState === newState && oldEffects === newEffects) {
                return null
            }

            requirementDemandStates[idx] = newState
            requirementCleanerEffects[idx] = newEffects
            delta.set(idx)

            return Unit
        }

        fun getAndResetDelta(dst: MutableCollection<InitialFactAp>) {
            delta.forEach { idx ->
                val graph = requirementGraphs[idx]
                val demandState = requirementDemandStates[idx]
                val cleanerEffects = requirementCleanerEffects[idx]
                dst.add(
                    AccessGraphInitialFactAp(
                        base, graph, demandState.exclusions, cleanerEffects
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
                    val demandState = requirementDemandStates[i]
                    val cleanerEffects = requirementCleanerEffects[i]
                    collection += AccessGraphInitialFactAp(
                        base, graph, demandState.exclusions, cleanerEffects
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

                val demandState = requirementDemandStates[graphIdx]
                val cleanerEffects = requirementCleanerEffects[graphIdx]
                collection += AccessGraphInitialFactAp(
                    base, graph, demandState.exclusions, cleanerEffects
                )
            }
        }
    }
}
