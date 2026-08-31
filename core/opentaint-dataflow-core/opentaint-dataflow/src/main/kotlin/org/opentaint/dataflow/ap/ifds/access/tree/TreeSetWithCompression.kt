package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

open class TreeSetWithCompression(maxInstIdx: Int, val manager: TreeApManager) {
    val edges = arrayOfNulls<AccessTreeNode?>(instructionStorageSize(maxInstIdx))

    private val interner = AccessTreeSoftInterner(manager)

    fun internIfRequired(node: AccessTreeNode): AccessTreeNode = interner.intern(node)
}
