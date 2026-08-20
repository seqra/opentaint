package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

open class TreeSetWithCompression(maxInstIdx: Int, val manager: TreeApManager) {
    val edges = arrayOfNulls<AccessTreeNode?>(instructionStorageSize(maxInstIdx))

    /**
     * Allocated on the first intern that actually reaches the interner, not on construction.
     *
     * There is one of these storages per premise trie node, and the analyzer builds millions of
     * them: an eagerly allocated interner was 2.27 M live objects in a ThingsBoard heap dump, of
     * which only 369 k (16.3 %) had ever created an [AccessTreeInterner]. The gates in [internImpl]
     * - one intern attempt in [INTERN_RATE], and only once some tree here has reached
     * [MIN_SIZE_TO_INTERN] - mean the other 83.7 % never had a use for it.
     *
     * Written only by the storage's own writer, like [edges] and [maxTreeSize] beside it.
     */
    private var interner: AccessTreeSoftInterner? = null

    private var operationsBeforeIntern = INTERN_RATE
    private var maxTreeSize = 0L

    private fun interner(): AccessTreeSoftInterner =
        interner ?: AccessTreeSoftInterner(manager).also { interner = it }

    fun internIfRequired(node: AccessTreeNode): AccessTreeNode {
        if (node.size < SIZE_TO_FORCE_INTERN) return node
        return interner().intern(node)
    }

    fun intern(idx: Int): Unit = internImpl(
        manager.cancellation,
        lastUpdated = edges[idx],
        size = edges.size,
        maxNodeSize = maxTreeSize,
        updateMaxNodeSize = { maxTreeSize = it },
        decOperations = { operationsBeforeIntern-- },
        resetOperation = { operationsBeforeIntern = INTERN_RATE },
        getInterner = { interner() },
        getNode = { edges[it] },
        setNode = { i, n -> edges[i] = n }
    )

    companion object {
        /**
         * `getInterner` is called only after every gate has passed, so a caller may allocate its
         * interner there rather than up front.
         */
        inline fun internImpl(
            cancellation: Cancellation,
            lastUpdated: AccessTreeNode?,
            size: Int,
            maxNodeSize: Long,
            updateMaxNodeSize: (Long) -> Unit,
            decOperations: () -> Int,
            resetOperation: () -> Unit,
            getInterner: () -> AccessTreeSoftInterner,
            crossinline getNode: (Int) -> AccessTreeNode?,
            crossinline setNode: (Int, AccessTreeNode) -> Unit,
        ) {
            lastUpdated?.let { updateMaxNodeSize(maxOf(maxNodeSize, it.size)) }

            if (decOperations() > 0) return
            if (maxNodeSize < MIN_SIZE_TO_INTERN) return
            resetOperation()

            getInterner().withInterner { interner, cache ->
                for (i in 0 until size) {
                    val node = getNode(i) ?: continue
                    setNode(i, node.internNodes(interner, cache))
                }
            }
        }

        const val MIN_SIZE_TO_INTERN = 100
        const val SIZE_TO_FORCE_INTERN = 100_000
        private const val INTERN_RATE = 100
    }
}
