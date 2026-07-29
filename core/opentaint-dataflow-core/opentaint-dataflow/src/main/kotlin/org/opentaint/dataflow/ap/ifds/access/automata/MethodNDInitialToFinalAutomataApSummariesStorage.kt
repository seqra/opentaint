package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodNDInitialToFinalAutomataApSummariesStorage(methodEntryPoint: CommonInst) :
    CommonNDF2FSummary<AutomataFinalAccess>(methodEntryPoint), AutomataFinalApAccess {
    private class Builder : NDF2FBBuilder<AutomataFinalAccess>(), AutomataFinalApAccess

    override fun createStorage(): Storage<AutomataFinalAccess> =
        object : DefaultNDF2FSummaryStorageWithAp<AutomataInitialAccess, AutomataFinalAccess>(
            methodEntryPoint
        ), AutomataInitialApAccess {
            override fun createBuilder(): NDF2FBBuilder<AutomataFinalAccess> = Builder()

            override fun createStorage(
                idx: Int,
            ): Storage<AutomataInitialAccess, AutomataFinalAccess> = FactStorage(idx)

            private inner class FactStorage(
                override val storageIdx: Int,
            ) : Storage<AutomataInitialAccess, AutomataFinalAccess> {
                private val accessStorage = hashSetOf<AutomataFinalAccess>()
                private val delta = arrayListOf<AutomataFinalAccess>()

                override fun add(
                    element: AutomataFinalAccess,
                ): Storage<AutomataInitialAccess, AutomataFinalAccess>? {
                    if (accessStorage.add(element)) {
                        delta += element
                        return this
                    }
                    return null
                }

                override fun getAndResetDelta(dst: MutableList<AutomataFinalAccess>) {
                    dst += delta
                    delta.clear()
                }

                override fun collectTo(dst: MutableList<AutomataFinalAccess>) {
                    dst += accessStorage
                }
            }
        }
}
