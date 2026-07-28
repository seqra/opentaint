package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSummary
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSummaryStorageWithAp
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodNDInitialToFinalAutomataApSummariesStorage(methodEntryPoint: CommonInst) :
    CommonNDF2FSummary<AutomataAccess>(methodEntryPoint), AutomataFinalApAccess {
    private class Builder : NDF2FBBuilder<AutomataAccess>(), AutomataFinalApAccess

    override fun createStorage(): Storage<AutomataAccess> =
        object : DefaultNDF2FSummaryStorageWithAp<AutomataAccess, AutomataAccess>(methodEntryPoint), AutomataInitialApAccess {
            override fun createBuilder(): NDF2FBBuilder<AutomataAccess> = Builder()

            override fun createStorage(idx: Int): Storage<AutomataAccess, AutomataAccess> = FactStorage(idx)

            private inner class FactStorage(
                override val storageIdx: Int,
            ) : Storage<AutomataAccess, AutomataAccess> {
                private val accessStorage = hashSetOf<AutomataAccess>()
                private val delta = arrayListOf<AutomataAccess>()

                override fun add(element: AutomataAccess): Storage<AutomataAccess, AutomataAccess>? {
                    if (accessStorage.add(element)) {
                        delta += element
                        return this
                    }
                    return null
                }

                override fun getAndResetDelta(dst: MutableList<AutomataAccess>) {
                    dst += delta
                    delta.clear()
                }

                override fun collectTo(dst: MutableList<AutomataAccess>) {
                    dst += accessStorage
                }
            }
        }
}
