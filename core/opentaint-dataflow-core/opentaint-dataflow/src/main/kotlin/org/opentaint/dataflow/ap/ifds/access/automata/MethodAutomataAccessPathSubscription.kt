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

class MethodAutomataAccessPathSubscription :
    CommonAPSub<AutomataInitialAccess, AutomataFinalAccess>(),
    AutomataInitialApAccess, AutomataFinalApAccess {

    override fun createZ2FSubStorage(
        callerEp: CommonInst,
    ): Z2FSubStorage<AutomataInitialAccess, AutomataFinalAccess> = Z2FFactGraphs()

    override fun createF2FSubStorage(
        callerEp: CommonInst,
    ): F2FSubStorage<AutomataInitialAccess, AutomataFinalAccess> = F2FFactGraphs()

    override fun createNDF2FSubStorage(
        callerEp: CommonInst,
    ): NDF2FSubStorage<AutomataInitialAccess, AutomataFinalAccess> = NdF2f(callerEp)

    private class Z2FFactGraphs : Z2FSubStorage<AutomataInitialAccess, AutomataFinalAccess> {
        private val facts = hashSetOf<AutomataFinalAccess>()

        override fun add(
            callerExitAp: AutomataFinalAccess,
        ): CommonZeroEdgeSubBuilder<AutomataFinalAccess>? {
            if (!facts.add(callerExitAp)) return null
            return ZeroEdgeSubBuilder().setNode(callerExitAp)
        }

        override fun find(
            dst: MutableList<CommonZeroEdgeSubBuilder<AutomataFinalAccess>>,
            summaryInitialFact: AutomataInitialAccess,
        ) {
            facts.mapNotNullTo(dst) {
                val delta = it.access.delta(summaryInitialFact)
                if (delta.isEmpty()) return@mapNotNullTo null

                ZeroEdgeSubBuilder().setNode(it)
            }
        }
    }

    private class F2FFactGraphs : F2FSubStorage<AutomataInitialAccess, AutomataFinalAccess> {
        private val edgeIndex = object2IntMap<Pair<AccessGraphInitialFactAp, AutomataFinalAccess>>()
        private val edges = arrayListOf<Pair<AccessGraphInitialFactAp, AutomataFinalAccess>>()

        private val graphIndex = GraphIndex()

        override fun add(
            callerInitialAp: InitialFactAp,
            callerExitAp: AutomataFinalAccess,
        ): CommonFactEdgeSubBuilder<AutomataFinalAccess>? {
            callerInitialAp as AccessGraphInitialFactAp

            val entry = Pair(callerInitialAp, callerExitAp)
            edgeIndex.getOrCreateIndex(entry) { newIndex ->
                edges.add(entry)

                updateGraphIndex(entry.second, newIndex)

                return FactEdgeSubBuilder()
                    .setCallerNode(callerExitAp)
                    .setCallerInitialAp(callerInitialAp)
                    .setCallerExclusion(callerInitialAp.exclusions)
            }

            return null
        }

        private fun updateGraphIndex(graph: AutomataFinalAccess, idx: Int) {
            graphIndex.add(graph.access, idx)
        }

        override fun find(
            dst: MutableList<CommonFactEdgeSubBuilder<AutomataFinalAccess>>,
            summaryInitialFact: AutomataInitialAccess,
            emptyDeltaRequired: Boolean,
        ) {
            if (!emptyDeltaRequired) {
                graphIndex.localizeIndexedGraphHasDeltaWithGraph(summaryInitialFact).forEach { edgeIdx ->
                    val (initialAp, final) = edges[edgeIdx]

                    val delta = final.access.delta(summaryInitialFact)
                    if (delta.isEmpty()) return@forEach

                    dst += FactEdgeSubBuilder()
                        .setCallerInitialAp(initialAp)
                        .setCallerNode(final)
                        .setCallerExclusion(initialAp.exclusions)
                }
            } else {
                collectEmptyDelta(dst, summaryInitialFact)
            }
        }

        private fun collectEmptyDelta(
            collection: MutableList<CommonFactEdgeSubBuilder<AutomataFinalAccess>>,
            summaryInitialFactAp: AutomataInitialAccess,
        ) {
            graphIndex.localizeIndexedGraphContainsAllGraph(summaryInitialFactAp).forEach { edgeIdx ->
                val (initialAp, final) = edges[edgeIdx]

                if (!final.access.containsAll(summaryInitialFactAp)) {
                    return@forEach
                }

                collection += FactEdgeSubBuilder()
                    .setCallerInitialAp(initialAp)
                    .setCallerNode(final)
                    .setCallerExclusion(initialAp.exclusions)
            }
        }
    }

    private class NdF2f(callerEp: CommonInst) :
        DefaultNDF2FSubStorageWithAp<AutomataInitialAccess, AutomataFinalAccess>(callerEp),
        AutomataInitialApAccess {
        private val graphIndex = GraphIndex()

        override fun createBuilder(): CommonFactNDEdgeSubBuilder<AutomataFinalAccess> =
            FactNDEdgeSubBuilder()

        private inner class FactStorage(
            private val storageIdx: Int,
        ) : Storage<AutomataInitialAccess, AutomataFinalAccess> {
            private val graphs = object2IntMap<AutomataFinalAccess>()
            private val graphList = arrayListOf<AutomataFinalAccess>()

            override fun add(element: AutomataFinalAccess): AutomataFinalAccess? {
                graphs.getOrCreateIndex(element) {
                    graphList.add(element)
                    graphIndex.add(element.access, storageIdx)
                    return element
                }

                return null
            }

            override fun collect(dst: MutableList<AutomataFinalAccess>) {
                dst.addAll(graphList)
            }

            override fun collect(
                dst: MutableList<AutomataFinalAccess>,
                summaryInitialFact: AutomataInitialAccess,
            ) {
                for (graph in graphList) {
                    if (graph.access.containsAll(summaryInitialFact)) {
                        dst.add(graph)
                    }
                }
            }
        }

        override fun createStorage(
            idx: Int,
        ): Storage<AutomataInitialAccess, AutomataFinalAccess> = FactStorage(idx)

        override fun relevantStorageIndices(summaryInitialFact: AutomataInitialAccess): BitSet =
            graphIndex.localizeIndexedGraphContainsAllGraph(summaryInitialFact)
    }
}

private class ZeroEdgeSubBuilder :
    CommonZeroEdgeSubBuilder<AutomataFinalAccess>(), AutomataFinalApAccess
private class FactEdgeSubBuilder :
    CommonFactEdgeSubBuilder<AutomataFinalAccess>(), AutomataFinalApAccess
private class FactNDEdgeSubBuilder :
    CommonFactNDEdgeSubBuilder<AutomataFinalAccess>(), AutomataFinalApAccess
