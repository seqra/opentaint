package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonAPSub
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactNDEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.CommonZeroEdgeSubBuilder
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSubStorageWithAp
import org.opentaint.dataflow.util.forEach
import org.opentaint.dataflow.util.getOrCreateIndex
import org.opentaint.dataflow.util.object2IntMap
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet

class MethodAutomataAccessPathSubscription : CommonAPSub<AutomataAccess, AutomataAccess>(),
    AutomataInitialApAccess, AutomataFinalApAccess {

    override fun createZ2FSubStorage(callerEp: CommonInst): Z2FSubStorage<AutomataAccess, AutomataAccess> = Z2FFactGraphs()

    override fun createF2FSubStorage(callerEp: CommonInst): F2FSubStorage<AutomataAccess, AutomataAccess> = F2FFactGraphs()

    override fun createNDF2FSubStorage(callerEp: CommonInst): NDF2FSubStorage<AutomataAccess, AutomataAccess> = NdF2f(callerEp)

    private class Z2FFactGraphs : Z2FSubStorage<AutomataAccess, AutomataAccess> {
        private val facts = hashSetOf<AutomataAccess>()

        override fun add(callerExitAp: AutomataAccess): CommonZeroEdgeSubBuilder<AutomataAccess>? {
            if (!facts.add(callerExitAp)) return null
            return ZeroEdgeSubBuilder().setNode(callerExitAp)
        }

        override fun find(
            dst: MutableList<CommonZeroEdgeSubBuilder<AutomataAccess>>,
            summaryInitialFact: AutomataAccess,
        ) {
            facts.mapNotNullTo(dst) {
                val delta = it.access.delta(summaryInitialFact.access)
                if (delta.isEmpty()) return@mapNotNullTo null

                ZeroEdgeSubBuilder().setNode(it)
            }
        }
    }

    private class F2FFactGraphs : F2FSubStorage<AutomataAccess, AutomataAccess> {
        private val edgeIndex = object2IntMap<Pair<AccessGraphInitialFactAp, AutomataAccess>>()
        private val edges = arrayListOf<Pair<AccessGraphInitialFactAp, AutomataAccess>>()

        private val graphIndex = GraphIndex()

        override fun add(
            callerInitialAp: InitialFactAp,
            callerExitAp: AutomataAccess,
        ): CommonFactEdgeSubBuilder<AutomataAccess>? {
            callerInitialAp as AccessGraphInitialFactAp

            val entry = Pair(callerInitialAp, callerExitAp)
            edgeIndex.getOrCreateIndex(entry) { newIndex ->
                edges.add(entry)

                updateGraphIndex(entry.second, newIndex)

                return FactEdgeSubBuilder()
                    .setCallerNode(callerExitAp)
                    .setCallerInitialAp(callerInitialAp)
                    .setCallerDemandState(callerInitialAp.demandState)
            }

            return null
        }

        private fun updateGraphIndex(graph: AutomataAccess, idx: Int) {
            graphIndex.add(graph.access, idx)
        }

        override fun find(
            dst: MutableList<CommonFactEdgeSubBuilder<AutomataAccess>>,
            summaryInitialFact: AutomataAccess,
            emptyDeltaRequired: Boolean,
        ) {
            if (!emptyDeltaRequired) {
                graphIndex.localizeIndexedGraphHasDeltaWithGraph(summaryInitialFact.access).forEach { edgeIdx ->
                    val (initialAp, final) = edges[edgeIdx]

                    val delta = final.access.delta(summaryInitialFact.access)
                    if (delta.isEmpty()) return@forEach

                    dst += FactEdgeSubBuilder()
                        .setCallerInitialAp(initialAp)
                        .setCallerNode(final)
                        .setCallerDemandState(initialAp.demandState)
                }
            } else {
                collectEmptyDelta(dst, summaryInitialFact)
            }
        }

        private fun collectEmptyDelta(
            collection: MutableList<CommonFactEdgeSubBuilder<AutomataAccess>>,
            summaryInitialFactAp: AutomataAccess,
        ) {
            graphIndex.localizeIndexedGraphContainsAllGraph(summaryInitialFactAp.access).forEach { edgeIdx ->
                val (initialAp, final) = edges[edgeIdx]

                if (!final.access.containsAll(summaryInitialFactAp.access)) {
                    return@forEach
                }

                collection += FactEdgeSubBuilder()
                    .setCallerInitialAp(initialAp)
                    .setCallerNode(final)
                    .setCallerDemandState(initialAp.demandState)
            }
        }
    }

    private class NdF2f(callerEp: CommonInst) :
        DefaultNDF2FSubStorageWithAp<AutomataAccess, AutomataAccess>(callerEp), AutomataInitialApAccess {
        private val graphIndex = GraphIndex()

        override fun createBuilder(): CommonFactNDEdgeSubBuilder<AutomataAccess> = FactNDEdgeSubBuilder()

        private inner class FactStorage(
            private val storageIdx: Int,
        ) : Storage<AutomataAccess, AutomataAccess> {
            private val graphs = object2IntMap<AutomataAccess>()
            private val graphList = arrayListOf<AutomataAccess>()

            override fun add(element: AutomataAccess): AutomataAccess? {
                graphs.getOrCreateIndex(element) {
                    graphList.add(element)
                    graphIndex.add(element.access, storageIdx)
                    return element
                }

                return null
            }

            override fun collect(dst: MutableList<AutomataAccess>) {
                dst.addAll(graphList)
            }

            override fun collect(dst: MutableList<AutomataAccess>, summaryInitialFact: AutomataAccess) {
                for (graph in graphList) {
                    if (graph.access.containsAll(summaryInitialFact.access)) {
                        dst.add(graph)
                    }
                }
            }
        }

        override fun createStorage(idx: Int): Storage<AutomataAccess, AutomataAccess> = FactStorage(idx)

        override fun relevantStorageIndices(summaryInitialFact: AutomataAccess): BitSet =
            graphIndex.localizeIndexedGraphContainsAllGraph(summaryInitialFact.access)
    }
}

private class ZeroEdgeSubBuilder : CommonZeroEdgeSubBuilder<AutomataAccess>(), AutomataFinalApAccess
private class FactEdgeSubBuilder : CommonFactEdgeSubBuilder<AutomataAccess>(), AutomataFinalApAccess
private class FactNDEdgeSubBuilder : CommonFactNDEdgeSubBuilder<AutomataAccess>(), AutomataFinalApAccess
