package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSetStorage
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesNDInitialToFinalBaseOnlyApSet(
    initialStatement: CommonInst,
    languageManager: LanguageManager,
    maxInstIdx: Int,
    override val apManager: BaseOnlyApManager,
) : CommonNDF2FSet<BaseOnlyAccess, BaseOnlyAccess>(initialStatement, languageManager, maxInstIdx),
    BaseOnlyFinalApAccess, BaseOnlyInitialApAccess {

    override fun mostAbstractPattern(base: AccessPathBase): BaseOnlyAccess = ABSTRACT_EMPTY_ACCESS

    override fun createApStorage(): ApStorage<BaseOnlyAccess, BaseOnlyAccess> =
        object : DefaultNDF2FSetStorage<BaseOnlyAccess, BaseOnlyAccess>() {
            override fun createStorage(): Storage<BaseOnlyAccess> = SetStorage(apManager)
        }

    private class SetStorage(private val manager: BaseOnlyApManager) : DefaultNDF2FSetStorage.Storage<BaseOnlyAccess> {
        private val set = LongOpenHashSet()

        override fun add(element: BaseOnlyAccess): BaseOnlyAccess? {
            if (element.isCollapsed) return null
            if (!set.add(element)) return null
            return element
        }

        override fun collect(dst: MutableList<BaseOnlyAccess>) {
            dst.addAll(set)
        }
    }
}
