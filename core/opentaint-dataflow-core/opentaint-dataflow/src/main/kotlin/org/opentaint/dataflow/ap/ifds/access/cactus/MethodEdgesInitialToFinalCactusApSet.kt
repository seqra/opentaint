package org.opentaint.dataflow.ap.ifds.access.cactus

import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.access.FactFlowState
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalCactusApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager
) : CommonF2FSet<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode>(methodInitialStatement),
    CactusInitialApAccess, CactusFinalApAccess {
    override fun createApStorage(): ApStorage<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode> =
        TaintedFactAccessEdgeStorage()

    override fun mostAbstractPattern(base: AccessPathBase): AccessPathWithCycles.AccessNode? = null

    private inner class TaintedFactAccessEdgeStorage :
        ApStorage<AccessPathWithCycles.AccessNode?, AccessCactus.AccessNode> {
        val sameInitialAccessEdges =
            Object2ObjectOpenHashMap<AccessPathWithCycles.AccessNode?, EdgeNonUniverseExclusionMergingStorage>()

        override fun add(
            statement: CommonInst,
            initial: AccessPathWithCycles.AccessNode?,
            final: AccessWithState<AccessCactus.AccessNode>
        ): AccessWithState<AccessCactus.AccessNode>? {
            val storage = sameInitialAccessEdges.getOrPut(initial) {
                EdgeNonUniverseExclusionMergingStorage(maxInstIdx, languageManager)
            }

            return storage.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<AccessPathWithCycles.AccessNode?, AccessWithState<AccessCactus.AccessNode>>>,
            statement: CommonInst,
            finalPattern: AccessPathWithCycles.AccessNode?,
        ) {
            sameInitialAccessEdges.forEach { (initial, storage) ->
                collectToListWithPostProcess(
                    dst,
                    { storage.allApAtStatement(it, statement) },
                    { initial to it }
                )
            }
        }

        override fun filter(
            dst: MutableList<AccessWithState<AccessCactus.AccessNode>>,
            statement: CommonInst,
            initial: AccessPathWithCycles.AccessNode?,
            finalPattern: AccessPathWithCycles.AccessNode?,
        ) {
            val storage = sameInitialAccessEdges[initial] ?: return
            storage.allApAtStatement(dst, statement)
        }
    }

    private class EdgeNonUniverseExclusionMergingStorage(
        maxInstIdx: Int, private val languageManager: LanguageManager
    ) {
        private val flowStates = arrayOfNulls<FactFlowState>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))
        private val edges = arrayOfNulls<AccessCactus.AccessNode>(MethodAnalyzerEdges.instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            accessWithState: AccessWithState<AccessCactus.AccessNode>,
        ): AccessWithState<AccessCactus.AccessNode>? {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val currentState = flowStates[edgeSetIdx]

            if (currentState == null) {
                flowStates[edgeSetIdx] = accessWithState.flowState
                edges[edgeSetIdx] = accessWithState.access
                return accessWithState
            }

            val currentAccess = edges[edgeSetIdx]!!
            val mergedState = currentState join accessWithState.flowState
            flowStates[edgeSetIdx] = mergedState

            val mergedAccess = currentAccess.mergeAdd(accessWithState.access)
            if (mergedAccess === currentAccess) {
                if (mergedState === currentState) return null

                return AccessWithState(mergedAccess, mergedState)
            }

            edges[edgeSetIdx] = mergedAccess
            return AccessWithState(mergedAccess, mergedState)
        }

        fun allApAtStatement(dst: MutableList<AccessWithState<AccessCactus.AccessNode>>, statement: CommonInst) {
            val edgeSetIdx = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
            val flowState = flowStates[edgeSetIdx] ?: return
            val access = edges[edgeSetIdx] ?: return
            dst += AccessWithState(access, flowState)
        }
    }
}
