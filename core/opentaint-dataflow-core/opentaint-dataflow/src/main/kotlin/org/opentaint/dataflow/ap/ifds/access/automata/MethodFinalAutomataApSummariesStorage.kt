package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalAutomataApSummariesStorage(methodEntryPoint: CommonInst) :
    CommonZ2FSummary<AutomataFinalAccess>(methodEntryPoint),
    AutomataFinalApAccess {

    override fun createStorage(): Storage<AutomataFinalAccess> = ApStorage()

    private class ApStorage : Storage<AutomataFinalAccess> {
        private var summaryAccess: AutomataFinalAccess? = null

        override fun add(edges: List<AutomataFinalAccess>, added: MutableList<Z2FBBuilder<AutomataFinalAccess>>) {
            for (edge in edges) {
                val current = summaryAccess
                if (current == null) {
                    summaryAccess = edge
                    added += ZeroToFactEdgeBuilderBuilder().setNode(edge)
                    continue
                }

                val merged = current.mergeAdd(edge)
                if (merged === current) continue
                summaryAccess = merged
                added += ZeroToFactEdgeBuilderBuilder().setNode(merged)
            }
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<AutomataFinalAccess>>) {
            summaryAccess?.let {
                dst += ZeroToFactEdgeBuilderBuilder().setNode(it)
            }
        }
    }

    private class ZeroToFactEdgeBuilderBuilder: Z2FBBuilder<AutomataFinalAccess>(), AutomataFinalApAccess
}
