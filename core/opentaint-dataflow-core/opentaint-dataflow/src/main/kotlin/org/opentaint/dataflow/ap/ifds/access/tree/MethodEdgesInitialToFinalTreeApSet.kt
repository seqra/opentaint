package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.util.PersistentIntSet
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalTreeApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager,
    override val apManager: TreeApManager,
) : CommonF2FSet<AccessPath.AccessNode?, AccessTree.AccessNode>(methodInitialStatement),
    TreeInitialApAccess, TreeFinalApAccess {

    override fun createApStorage(): ApStorage<AccessPath.AccessNode?, AccessTree.AccessNode> =
        TaintedFactAccessEdgeStorage()

    override fun mostAbstractPattern(base: AccessPathBase): AccessPath.AccessNode? = null

    private inner class TaintedFactAccessEdgeStorage : ApStorage<AccessPath.AccessNode?, AccessTree.AccessNode> {
        private val sameInitialAccessEdges = IF2FFStorage(maxInstIdx, languageManager, apManager)

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
        val maxInstIdx: Int,
        private val languageManager: LanguageManager,
        manager: TreeApManager,
    ) : AccessBasedStorage<IF2FFStorage>(manager) {
        val current = EdgeNonUniverseExclusionMergingStorage(maxInstIdx, languageManager, manager)

        override fun createStorage(): IF2FFStorage =
            IF2FFStorage(maxInstIdx, languageManager, manager)

        override fun printStorageNode(): String = current.toString()
    }

    private class EdgeNonUniverseExclusionMergingStorage(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
        manager: TreeApManager,
    ): TreeSetWithCompression(maxInstIdx, manager) {
        private val exclusions = arrayOfNulls<PersistentIntSet>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            accessWithExclusion: AccessWithExclusion<AccessTree.AccessNode>
        ): AccessWithExclusion<AccessTree.AccessNode>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val addedExclusion = accessWithExclusion.exclusion.accessors()

            val currentAccess = edges[edgeSetIdx]
            if (currentAccess == null) {
                exclusions[edgeSetIdx] = addedExclusion?.clone()
                edges[edgeSetIdx] = internIfRequired(accessWithExclusion.access)
                return accessWithExclusion
            }

            val currentExclusion = exclusions[edgeSetIdx]
            val exclusionModified = if (currentExclusion == null) {
                if (addedExclusion == null) {
                    false
                } else {
                    exclusions[edgeSetIdx] = addedExclusion.clone()
                    true
                }
            } else {
                val initial = currentExclusion.size
                if (addedExclusion != null) {
                    currentExclusion.addAll(addedExclusion)
                }
                initial != currentExclusion.size
            }

            val mergedAccess = currentAccess.mergeAdd(accessWithExclusion.access)
            if (mergedAccess === currentAccess) {
                if (!exclusionModified) return null

                return AccessWithExclusion(mergedAccess, ExclusionSet.create(exclusions[edgeSetIdx]))
            }

            edges[edgeSetIdx] = internIfRequired(mergedAccess)
            intern(edgeSetIdx)

            return AccessWithExclusion(mergedAccess, ExclusionSet.create(exclusions[edgeSetIdx]))
        }

        fun allApAtStatement(dst: MutableList<AccessWithExclusion<AccessTree.AccessNode>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val access = edges[edgeSetIdx] ?: return
            val currentExclusion = exclusions[edgeSetIdx]
            dst += AccessWithExclusion(access, ExclusionSet.create(currentExclusion))
        }

        fun ExclusionSet.accessors(): PersistentIntSet? {
            if (this !is ExclusionSet.Concrete) return null
            return set
        }
    }
}
