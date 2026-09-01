package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalTreeApSet(
    methodInitialStatement: CommonInst,
    @Suppress("UNUSED_PARAMETER") maxInstIdx: Int,
    private val languageManager: LanguageManager,
    override val apManager: TreeApManager,
) : CommonF2FSet<AccessPath.AccessNode?, AccessTree.AccessNode>(methodInitialStatement),
    TreeInitialApAccess, TreeFinalApAccess {

    override fun createApStorage(): ApStorage<AccessPath.AccessNode?, AccessTree.AccessNode> =
        TaintedFactAccessEdgeStorage()

    override fun mostAbstractPattern(base: AccessPathBase): AccessPath.AccessNode? = null

    private inner class TaintedFactAccessEdgeStorage : ApStorage<AccessPath.AccessNode?, AccessTree.AccessNode> {
        private val sameInitialAccessEdges = IF2FFStorage(languageManager, apManager)

        override fun add(
            statement: CommonInst,
            initial: AccessPath.AccessNode?,
            final: AccessWithExclusion<AccessTree.AccessNode>,
        ): AccessWithExclusion<AccessTree.AccessNode>? {
            val storage = sameInitialAccessEdges.getOrCreateNode(initial).current

            return storage.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<AccessPath.AccessNode?, AccessWithExclusion<AccessTree.AccessNode>>>,
            statement: CommonInst,
            finalPattern: AccessPath.AccessNode?,
        ) {
            sameInitialAccessEdges.forEachNode { initial, storage ->
                collectToListWithPostProcess(
                    dst,
                    { storage.current.allApAtStatement(it, statement) },
                    { initial to it }
                )
            }
        }

        override fun filter(
            dst: MutableList<AccessWithExclusion<AccessTree.AccessNode>>,
            statement: CommonInst,
            initial: AccessPath.AccessNode?,
            finalPattern: AccessPath.AccessNode?,
        ) {
            val storage = sameInitialAccessEdges.find(initial)?.current ?: return
            storage.allApAtStatement(dst, statement)
        }
    }

    private class IF2FFStorage(
        private val languageManager: LanguageManager,
        manager: TreeApManager,
    ) : AccessBasedStorage<IF2FFStorage>(manager) {
        val current = EdgeNonUniverseExclusionMergingStorage(languageManager, manager)

        override fun createStorage(): IF2FFStorage =
            IF2FFStorage(languageManager, manager)

        override fun printStorageNode(): String = current.toString()
    }

    private class EdgeNonUniverseExclusionMergingStorage(
        private val languageManager: LanguageManager,
        manager: TreeApManager,
    ): TreeSetWithCompression(2, manager) {

        fun add(
            statement: CommonInst,
            accessWithExclusion: AccessWithExclusion<AccessTree.AccessNode>
        ): AccessWithExclusion<AccessTree.AccessNode>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val row = rowsForWrite(edgeSetIdx)
            val offset = offsetOf(row, edgeSetIdx)
            val currentExclusion = row.values[offset + EXCLUSION] as ExclusionSet?

            if (currentExclusion == null) {
                row.values[offset + ACCESS] = internIfRequired(accessWithExclusion.access)
                row.values[offset + EXCLUSION] = accessWithExclusion.exclusion
                return accessWithExclusion
            }

            val mergedExclusion = currentExclusion.union(accessWithExclusion.exclusion)
            row.values[offset + EXCLUSION] = mergedExclusion

            val currentAccess = row.values[offset + ACCESS] as AccessTree.AccessNode
            val (mergedAccess, accessDelta) = currentAccess.mergeAddDelta(accessWithExclusion.access)
            if (accessDelta != null) row.values[offset + ACCESS] = internIfRequired(mergedAccess)

            if (mergedExclusion !== currentExclusion) {
                return AccessWithExclusion(mergedAccess, mergedExclusion)
            }
            if (accessDelta == null) return null
            return AccessWithExclusion(accessDelta, mergedExclusion)
        }

        fun allApAtStatement(dst: MutableList<AccessWithExclusion<AccessTree.AccessNode>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val row = rows() ?: return
            val offset = offsetOf(row, edgeSetIdx)
            if (offset < 0) return
            val currentExclusion = row.values[offset + EXCLUSION] as ExclusionSet? ?: return
            val access = row.values[offset + ACCESS] as AccessTree.AccessNode? ?: return
            dst += AccessWithExclusion(access, currentExclusion)
        }

        private companion object {
            private const val ACCESS = 0
            private const val EXCLUSION = 1
        }
    }
}
