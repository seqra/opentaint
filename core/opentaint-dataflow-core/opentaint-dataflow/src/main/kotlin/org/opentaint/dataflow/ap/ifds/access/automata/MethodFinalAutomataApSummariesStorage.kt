package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSummary
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodFinalAutomataApSummariesStorage(methodEntryPoint: CommonInst) :
    CommonZ2FSummary<AutomataAccess>(methodEntryPoint),
    AutomataFinalApAccess {

    override fun createStorage(): Storage<AutomataAccess> = ApStorage()

    private class ApStorage : Storage<AutomataAccess> {
        private val storage = AccessGraphStorageWithCompression()

        override fun add(edges: List<AutomataAccess>, added: MutableList<Z2FBBuilder<AutomataAccess>>) {
            check(edges.all { it.cleanerEffects.isEmpty })
            edges.forEach { storage.add(it.access) }
            storage.mapAndResetDelta {
                added += ZeroToFactEdgeBuilderBuilder()
                    .setNode(AutomataAccess(it, AnyFieldCleanerEffects.Empty))
            }
        }

        override fun collectEdges(dst: MutableList<Z2FBBuilder<AutomataAccess>>) {
            collectToListWithPostProcess(
                dst,
                { storage.allGraphsTo(it) },
                {
                    ZeroToFactEdgeBuilderBuilder()
                        .setNode(AutomataAccess(it, AnyFieldCleanerEffects.Empty))
                }
            )
        }
    }

    private class ZeroToFactEdgeBuilderBuilder: Z2FBBuilder<AutomataAccess>(), AutomataFinalApAccess
}
