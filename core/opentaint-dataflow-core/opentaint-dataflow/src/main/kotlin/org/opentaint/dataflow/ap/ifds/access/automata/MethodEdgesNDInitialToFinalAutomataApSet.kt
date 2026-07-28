package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSetStorage
import org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesNDInitialToFinalAutomataApSet(
    val apManager: AutomataApManager,
    initialStatement: CommonInst,
    languageManager: LanguageManager,
    maxInstIdx: Int,
) : CommonNDF2FSet<AutomataAccess, AutomataAccess>(initialStatement, languageManager, maxInstIdx),
    AutomataInitialApAccess, AutomataFinalApAccess {
    override fun createApStorage() = object : DefaultNDF2FSetStorage<AutomataAccess, AutomataAccess>() {
        override fun createStorage(): Storage<AutomataAccess> = DefaultStorage()
    }

    override fun mostAbstractPattern(base: AccessPathBase): AutomataAccess =
        AutomataAccess(apManager.emptyGraph(), AnyFieldCleanerEffects.Empty)

    private class DefaultStorage : DefaultNDF2FSetStorage.Storage<AutomataAccess> {
        private val storage = hashSetOf<AutomataAccess>()
        override fun add(element: AutomataAccess): AutomataAccess? =
            if (storage.add(element)) element else null

        override fun collect(dst: MutableList<AutomataAccess>) {
            dst.addAll(storage)
        }
    }
}
