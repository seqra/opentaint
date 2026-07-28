package org.opentaint.dataflow.ap.ifds.access.cactus

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSetStorage
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesNDInitialToFinalCactusApSet(
    initialStatement: CommonInst,
    languageManager: LanguageManager,
    maxInstIdx: Int,
) : CommonNDF2FSet<CactusInitialAccess, CactusFinalAccess>(
    initialStatement, languageManager, maxInstIdx
), CactusFinalApAccess, CactusInitialApAccess {
    override fun createApStorage() =
        object : DefaultNDF2FSetStorage<CactusInitialAccess, CactusFinalAccess>() {
            override fun createStorage(): Storage<CactusFinalAccess> = DefaultStorage()
        }

    override fun mostAbstractPattern(base: AccessPathBase): CactusInitialAccess =
        CactusInitialAccess(null, org.opentaint.dataflow.ap.ifds.access.AnyFieldCleanerEffects.Empty)

    private class DefaultStorage : DefaultNDF2FSetStorage.Storage<CactusFinalAccess> {
        private var current: CactusFinalAccess? = null

        override fun add(element: CactusFinalAccess): CactusFinalAccess? {
            val cur = current
            if (cur == null) {
                current = element
                return element
            }

            val merged = cur.mergeAdd(element)
            if (merged === cur) return null
            return merged.also { current = it }
        }

        override fun collect(dst: MutableList<CactusFinalAccess>) {
            current?.let { dst.add(it) }
        }
    }
}
