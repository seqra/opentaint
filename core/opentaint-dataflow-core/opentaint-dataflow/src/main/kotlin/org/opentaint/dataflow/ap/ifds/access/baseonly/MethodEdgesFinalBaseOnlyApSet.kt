package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSet
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesFinalBaseOnlyApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager,
    override val apManager: BaseOnlyApManager,
) : CommonZ2FSet<BaseOnlyAccess>(methodInitialStatement), BaseOnlyFinalApAccess {
    override fun createApStorage(): ApStorage<BaseOnlyAccess> =
        ZeroInitialFactEdges(maxInstIdx, languageManager)

    private class ZeroInitialFactEdges(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
    ) : ApStorage<BaseOnlyAccess> {
        private val edges = arrayOfNulls<LongOpenHashSet>(instructionStorageSize(maxInstIdx))

        override fun addEdge(statement: CommonInst, accessPath: BaseOnlyAccess): BaseOnlyAccess? {
            if (accessPath.isCollapsed) return null
            val idx = instructionStorageIdx(statement, languageManager)
            val set = edges[idx] ?: LongOpenHashSet().also { edges[idx] = it }
            if (!set.add(accessPath)) return null
            return accessPath
        }

        override fun collectApAtStatement(statement: CommonInst, dst: MutableList<BaseOnlyAccess>) {
            edges[instructionStorageIdx(statement, languageManager)]?.let { dst.addAll(it) }
        }
    }
}
