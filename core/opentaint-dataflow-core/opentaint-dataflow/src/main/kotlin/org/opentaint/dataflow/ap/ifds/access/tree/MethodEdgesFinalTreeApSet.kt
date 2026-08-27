package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.EdgeStoreDiagnostics
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSet
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

class MethodEdgesFinalTreeApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager,
    override val apManager: TreeApManager,
) : CommonZ2FSet<AccessTreeNode>(methodInitialStatement), TreeFinalApAccess {
    override fun createApStorage(): ApStorage<AccessTreeNode> =
        ZeroInitialFactEdges(maxInstIdx, languageManager, apManager)

    private class ZeroInitialFactEdges(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
        manager: TreeApManager,
    ): TreeSetWithCompression(maxInstIdx, manager), ApStorage<AccessTreeNode> {
        override fun addEdge(statement: CommonInst, accessPath: AccessTreeNode): AccessTreeNode? {
            val factSetIdx = instructionStorageIdx(statement, languageManager)
            val factSet = edges[factSetIdx]

            if (factSet == null) {
                edges[factSetIdx] = internIfRequired(accessPath)
                if (EdgeStoreDiagnostics.enabled) {
                    EdgeStoreDiagnostics.recordSlotOpened(accessPath.size)
                    EdgeStoreDiagnostics.recordRootBreadth(accessPath.accessorCount())
                }
                return accessPath
            }

            val merged = factSet.mergeAdd(accessPath)
            // The identity guard runs FIRST. Compressing before it would let a merge that added
            // nothing still rebuild the node, so `merged === factSet` would fail and the whole tree
            // would re-propagate for no new fact.
            if (merged === factSet) {
                return null
            }
            val mergedFacts =
                if (TreeApManager.ABSORB_SIBLINGS) merged.compressAbsorbCoveredSiblings() else merged

            if (EdgeStoreDiagnostics.enabled) {
                EdgeStoreDiagnostics.recordMerge(factSet.size, mergedFacts.size)
                EdgeStoreDiagnostics.recordRootBreadth(mergedFacts.accessorCount())
            }
            edges[factSetIdx] = internIfRequired(mergedFacts)
            intern(factSetIdx)
            return mergedFacts
        }

        override fun collectApAtStatement(statement: CommonInst, dst: MutableList<AccessTreeNode>) {
            dst += edges[instructionStorageIdx(statement, languageManager)] ?: return
        }
    }
}
