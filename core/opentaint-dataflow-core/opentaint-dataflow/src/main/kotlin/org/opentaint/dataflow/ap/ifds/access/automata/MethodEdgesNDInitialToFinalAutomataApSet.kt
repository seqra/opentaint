package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSetStorage
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesNDInitialToFinalAutomataApSet(
    val apManager: AutomataApManager,
    initialStatement: CommonInst,
    languageManager: LanguageManager,
    maxInstIdx: Int,
) : CommonNDF2FSet<AutomataInitialAccess, AutomataFinalAccess>(
    initialStatement, languageManager, maxInstIdx
),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createApStorage() =
        object : DefaultNDF2FSetStorage<AutomataInitialAccess, AutomataFinalAccess>() {
        override fun createStorage(): Storage<AutomataFinalAccess> = DefaultStorage()
    }

    override fun mostAbstractPattern(base: AccessPathBase): AutomataInitialAccess =
        apManager.emptyGraph()

    private class DefaultStorage : DefaultNDF2FSetStorage.Storage<AutomataFinalAccess> {
        private val storage = hashSetOf<AutomataFinalAccess>()
        override fun add(element: AutomataFinalAccess): AutomataFinalAccess? =
            if (storage.add(element)) element else null

        override fun collect(dst: MutableList<AutomataFinalAccess>) {
            dst.addAll(storage)
        }
    }
}
