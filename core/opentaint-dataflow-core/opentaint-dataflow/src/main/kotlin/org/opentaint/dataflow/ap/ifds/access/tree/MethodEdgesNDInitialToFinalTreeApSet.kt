package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.ndf2f.DefaultNDF2FSetStorage
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesNDInitialToFinalTreeApSet(
    methodInitialStatement: CommonInst,
    maxInstIdx: Int,
    languageManager: LanguageManager,
    override val apManager: TreeApManager,
) : CommonNDF2FSet<AccessPath.AccessNode?, AccessTree.AccessNode>(methodInitialStatement, languageManager, maxInstIdx),
    TreeInitialApAccess, TreeFinalApAccess {

    override fun createApStorage() = object : DefaultNDF2FSetStorage<AccessPath.AccessNode?, AccessTree.AccessNode>() {
        override fun createStorage(): Storage<AccessTree.AccessNode> = DefaultStorage()
    }

    override fun mostAbstractPattern(base: AccessPathBase): AccessPath.AccessNode? = null

    private class DefaultStorage : DefaultNDF2FSetStorage.Storage<AccessTree.AccessNode> {
        private var current: AccessTree.AccessNode? = null

        override fun add(element: AccessTree.AccessNode): AccessTree.AccessNode? {
            val cur = current
            if (cur == null) {
                current = element
                return element
            }

            val mergedAccess = cur.mergeAdd(element)
            // The identity guard runs FIRST -- see the note in MethodEdgesFinalTreeApSet. This is
            // the third store that propagates the WHOLE merged fact rather than the delta, so a
            // rebuild here costs the same re-propagation as it does there.
            if (mergedAccess === cur) return null

            val mergedFacts =
                if (TreeApManager.ABSORB_SIBLINGS) mergedAccess.compressAbsorbCoveredSiblings() else mergedAccess
            current = mergedFacts
            return mergedFacts
        }

        override fun collect(dst: MutableList<AccessTree.AccessNode>) {
            current?.let { dst.add(it) }
        }
    }
}
