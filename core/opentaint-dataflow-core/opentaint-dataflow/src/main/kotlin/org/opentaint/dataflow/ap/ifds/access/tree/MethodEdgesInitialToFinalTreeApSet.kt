package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.access.FactDemandState
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
            final: AccessWithState<AccessTree.AccessNode>,
        ): AccessWithState<AccessTree.AccessNode>? {
            val storage = sameInitialAccessEdges.getOrCreateNode(initial).current

            return storage.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<AccessPath.AccessNode?, AccessWithState<AccessTree.AccessNode>>>,
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
            dst: MutableList<AccessWithState<AccessTree.AccessNode>>,
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
        private val demandStates = arrayOfNulls<FactDemandState>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            accessWithState: AccessWithState<AccessTree.AccessNode>
        ): AccessWithState<AccessTree.AccessNode>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val currentState = demandStates[edgeSetIdx]

            if (currentState == null) {
                demandStates[edgeSetIdx] = accessWithState.demandState
                edges[edgeSetIdx] = internIfRequired(accessWithState.access)
                return accessWithState
            }

            val mergedState = currentState join accessWithState.demandState
            demandStates[edgeSetIdx] = mergedState

            val currentAccess = edges[edgeSetIdx]!!
            val mergedAccess = currentAccess.mergeAdd(accessWithState.access)
            if (mergedAccess === currentAccess) {
                if (mergedState === currentState) return null

                return AccessWithState(mergedAccess, mergedState)
            }

            edges[edgeSetIdx] = internIfRequired(mergedAccess)
            intern(edgeSetIdx)

            return AccessWithState(mergedAccess, mergedState)
        }

        fun allApAtStatement(dst: MutableList<AccessWithState<AccessTree.AccessNode>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val demandState = demandStates[edgeSetIdx] ?: return
            val access = edges[edgeSetIdx] ?: return
            dst += AccessWithState(access, demandState)
        }
    }
}
